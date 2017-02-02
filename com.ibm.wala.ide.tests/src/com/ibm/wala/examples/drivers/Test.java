import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAArrayReferenceInstruction;
import com.ibm.wala.ssa.SSACheckCastInstruction;
import com.ibm.wala.ssa.SSAFieldAccessInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.ssa.SSALoadMetadataInstruction;
import com.ibm.wala.ssa.SSANewInstruction;

// 1. synchronized (this)                       //PS - vn(n>=1) is used for single method, v1=this, v2=par1, v3=par2... ; for static methods, there is not "this", so v1=par1   
    if (lock.lock_name_vn == 1 && !im.isStatic()) { //vn=1 & !im.isStatic, 'this'
      lock.lock_class = im.getDeclaringClass().toString();
      lock.lock_name = "THIS";
    } 
    // 2. synchronized (argu), agru from method parameters        
    else if (!im.isStatic() && lock.lock_name_vn-1 <= ir.getNumberOfParameters()
        || im.isStatic() && lock.lock_name_vn <= ir.getNumberOfParameters()) { //vn in ([par1=this,] par2, par3, par4 ...)  
      int index = getSSAIndexBySSA(ssas, ssa); 
      if (index == -1) {
        System.err.println("ERROR - sync(argu) - (index = -1)");
      } else {
        lock.lock_class = "???????from method parameter, filtered now; actually it should be upward searched to find the fields";  // TODO
        //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
        lock.lock_name = "VARIABLE - ARGU- "+ ir.getLocalNames(index, lock.lock_name_vn)[0];  //should be found for this particular situation  #only for this kind of synchronized_lock now
      }
    }
    // 3. synchronized(class/object/this.object), not synchronized(xxx.object)
    else { //vn > maxOfParameters, that is, vn is not 'this' and parameters of the method
      int index = getSSAIndexByDefvn(ssas, lock.lock_name_vn, "3.synchronized(class/object/this.object)");;
      if (index == -1) { //phi,pi can't be found in ssas,TODO if needed; Eg, phi like v49 = phi v37,v35, eg, sync(block) in Balancer$Source.getBlockList()J
        System.err.println("ERROR - sync(class/obj/this.obj) - (index = -1) - - SSA:" + ssa);
        //System.err.println("ERROR - " + "funcname: " + functionname);
        //System.err.println("ERROR - " + "ssa: " + ssa);
        //System.err.println("ERROR - " + "lock_type: " + lock.lock_type);
        lock.lock_class = im.getDeclaringClass().toString(); //!!!!
        lock.lock_name = "?????eg phi, Usually local obj? filter it ??"; //Eg, sync(block) in Balancer$Source.getBlockList()J
      } else {
        /*
        System.err.println("previous ssa: " + ssas[index]);
        */
        // 3.1 synchronized (ClassName.class from LoadMetadata)   #only two org.apache.hadoop.conf.Configuration.<init>s are not static methods
        if (ssas[index] instanceof SSALoadMetadataInstruction) {
          SSALoadMetadataInstruction loadssa = (SSALoadMetadataInstruction) ssas[index];
          //System.err.println("synchronized (ClassName.class) - " + ssas[index] + " in a static " + im.isStatic() + " method?");
          lock.lock_class = loadssa.getToken().toString();    //previous usage should be wrong: im.getDeclaringClass().toString();
          lock.lock_name = "CLASS"; //((SSALoadMetadataInstruction)ssas[index]).getType().toString();
          //System.err.println("!!!!!!!!!!!!!!!!!!!!!!!!! - synchronized (ClassName.class) - " + functionname + "   class - " + lock.lock_class);
        }
        // 3.2 synchronized (this.object/object from GetField)   #eg, like "v2=getfield<xx..xx>v1"   //whether "getstatic" SSAs like "v2=getstatic<xx..xx>" is involved or not?
        else if (ssas[index] instanceof SSAFieldAccessInstruction) {
          /** WARN - ???
           * funcname: org.apache.hadoop.hdfs.server.balancer.Balancer$Source.dispatchBlocks()V
           * synchronized(Balancer.this) 
           * previous ssa - 41 = getfield < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> > 1
           * lock_name: < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> >
           */               
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    //verified: = im.getDeclaringClass().toString(); 
          lock.lock_name = "VARIABLE - GetField- " + fieldssa.getDeclaredField().toString();
        } 
        // 3.3 synchronized (object from a call - Invokexxx + GetField) 
        else if (ssas[index] instanceof SSAInvokeInstruction) {
          SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index];
          if (invokessa.isDispatch()) {      //3.3.1 invokeinterface?/invokevirtual + getfield    #eg, 87 = invokevirtual < Application, Ljava/lang/Process, getInputStream()Ljava/io/InputStream; > 85 @352 exception:86
            int usevn = invokessa.getUse(0); 
            int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from invokevitural)");
            if (index_usevn == -1) { 
              System.err.println("ERROR - sync(object coming from invokevitural) - (index = -1)");
            } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
              System.err.println("ERROR - sync(object coming from invokevitural) - !SSAFieldAccessInstruction");
            } else {
              SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
              lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
              lock.lock_name = "VARIABLE - InvokeVirtual/InvokeInterface+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
            }
          } else if (invokessa.isStatic()) { //3.3.2 invokestatic + getfield    #eg, v27 = invokestatic < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer, access$2000(Lorg/apache/hadoop/hdfs/server/balancer/Balancer;)Ljava/util/Map; > v25 @75 exception:26
            java.util.Set<CGNode> set = cg.getPossibleTargets(function, invokessa.getCallSite());
            if (set.size() == 0) {
              System.err.println("invokessa.getCallSite - " + invokessa.getCallSite());
              System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size = 0 - because the class's SUPERCLASS isn't included in these JarFiles"); // for Test, how to solve the problem??
            }
            if (set.size() >  1) System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size > 1"); // for Test, how to solve the problem??
            if (set.size() > 0) {            //JX: because I haven't yet added "hadoop-common"
              CGNode n = set.iterator().next(); 
              SSAInstruction[] invokessas = n.getIR().getInstructions();
              for (int i=0; i<invokessas.length; i++)                            
                if (invokessas[i] instanceof SSAFieldAccessInstruction) {     //like, a "getField" ssa in Balancer.access$2000
                  lock.lock_class = ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().getDeclaringClass().toString();
                  lock.lock_name = "VARIABLE - InvokeStatic+GetField- " + ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().toString();
                  break;
                }
            }
          } else if (invokessa.isSpecial()) { // 3.3.3 invokespecial?
            lock.lock_class = "????????invokespecial";  //like invokeinterface/invokevirtual?, that is, invokessa.getDeclaredTarget().getDeclaringClass().toString();
            lock.lock_name = "InvokeSpecial- " + invokessa.getDeclaredTarget().toString();
            System.err.println("WARN - SSAInvokeInstruction isSpecial - " + invokessa);
          } else 
            System.err.println("ERROR - other SSAInvokeInstruction? - " + invokessa);
        }
        // 3.4 synchronized (object from CheckCast + InvokeVirtual + GetField)
        else if (ssas[index] instanceof SSACheckCastInstruction) {
          SSACheckCastInstruction checkcastssa = (SSACheckCastInstruction) ssas[index];
          int usevn = checkcastssa.getUse(0); 
          int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from chestcast<+invokevitural>)");
          if (index_usevn == -1) { 
            System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - (index = -1)");
          } else if (!(ssas[index_usevn] instanceof SSAInvokeInstruction)) { 
            System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - !SSAInvokeInstruction");
          } else {
            SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index_usevn];
            int usevn2 = invokessa.getUse(0); 
            int index_usevn2 = getSSAIndexByDefvn(ssas, usevn2, "sync(object coming from <chestcast+>invokevitural)");
            if (index_usevn2 == -1) { 
              System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - (index = -1) -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
            } else if (!(ssas[index_usevn2] instanceof SSAFieldAccessInstruction)) { 
              System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - !SSAFieldAccessInstruction -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
            } else {
              SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn2];
              lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
              lock.lock_name = "VARIABLE - CheckCast+InvokeVirtual+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
            }
          }
        }
        // 3.5 synchronized (object from ArrayReference + GetField)
        else if (ssas[index] instanceof SSAArrayReferenceInstruction) {
          SSAArrayReferenceInstruction arrayrefssa = (SSAArrayReferenceInstruction) ssas[index];
          int usevn = arrayrefssa.getUse(0); 
          int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object from ArrayReference + GetField)");
          if (index_usevn == -1) { 
            System.err.println("ERROR - sync(object from ArrayReference <+ GetField>) - (index = -1)");
          } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
            System.err.println("ERROR - sync(object from <ArrayReference +> GetField) - !SSAFieldAccessInstruction");
          } else {
            SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
            lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
            lock.lock_name = "VARIABLE - ArrayReference+GetField- " + "ELEMENT" + " in " + fieldssa.getDeclaredField().toString(); //ps-ELEMENT=arrayrefssa.getElementType();  //jx - "getDeclaredTarget" is part of getCallSite
          }
        }
        // 3.6 synchronized (object from New)  must be local object??????
        else if (ssas[index] instanceof SSANewInstruction) {
          //SSANewInstruction newssa = (SSANewInstruction) ssas[index];
          lock.lock_class = im.getDeclaringClass().toString();    
          //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
          int originalindex = getSSAIndexBySSA(ssas, ssa);
          if (originalindex == -1) {
            System.err.println("ERROR - sync(obj from New) - (originalindex = -1)");
            lock.lock_name = "VARIABLE - New- " + "LOCALVAR-???" + " in " + im.getSignature();
          } else {
            lock.lock_name = "VARIABLE - New- " + "LOCALVAR-" + ir.getLocalNames(originalindex, lock.lock_name_vn)[0] + " in " + im.getSignature();  
          }
        }
        // 3.7 other synchronized (xx), that is, other SSAInstructions
        else {
          //TODO - maybe something
          System.err.println("WARN - other SSAInstruction, please have a look - " + ssas[index]);
        }
      }//index != -1, ie, can find index
    }//end-3.
    
    // Print for single lock if needed
    /*
    System.err.println("funcname: " + functionname);
    System.err.println("ssa: " + ssa);
    //System.err.println("lock_type: " + lock.lock_type);
    System.err.println("lock_class: " + lock.lock_class);
    System.err.println("lock_name: " + lock.lock_name);
    */
  }
  
public static void trackSSAsBackToGetPreciseLockForSyncCS_bk2(CGNode function, IMethod im, IR ir, SSAInstruction[] ssas, SSAInstruction ssa, LockInfo lock) {
    
    // 1. synchronized (this)                       //PS - vn(n>=1) is used for single method, v1=this, v2=par1, v3=par2... ; for static methods, there is not "this", so v1=par1   
    if (lock.lock_name_vn == 1 && !im.isStatic()) { //vn=1 & !im.isStatic, 'this'
      lock.lock_class = im.getDeclaringClass().toString();
      lock.lock_name = "THIS";
      return ;
    } 
    
    // 2. synchronized (argu), agru from method parameters        
    if (!im.isStatic() && lock.lock_name_vn-1 <= ir.getNumberOfParameters()
        || im.isStatic() && lock.lock_name_vn <= ir.getNumberOfParameters()) { //vn in ([par1=this,] par2, par3, par4 ...)  
      int index = getSSAIndexBySSA(ssas, ssa); 
      if (index == -1) {
        System.err.println("ERROR - sync(argu) - (index = -1)");
      } else {
        lock.lock_class = "???????from method parameter, filtered now; actually it should be upward searched to find the fields";  // TODO
        //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
        lock.lock_name = "VARIABLE - ARGU- "+ ir.getLocalNames(index, lock.lock_name_vn)[0];  //should be found for this particular situation  #only for this kind of synchronized_lock now
      }
      return ;
    }
    
    // 3. synchronized(class/object/this.object), not synchronized(xxx.object)    //ie, vn > maxOfParameters, that is, vn is not 'this' and parameters of the method
    int index = getSSAIndexByDefvn(ssas, lock.lock_name_vn, "3.synchronized(class/object/this.object)");;
    if (index == -1) { //phi,pi can't be found in ssas,TODO if needed; Eg, phi like v49 = phi v37,v35, eg, sync(block) in Balancer$Source.getBlockList()J
      System.err.println("ERROR - sync(class/obj/this.obj) - (index = -1) - - SSA:" + ssa);
      //System.err.println("ERROR - " + "funcname: " + functionname);
      //System.err.println("ERROR - " + "ssa: " + ssa);
      //System.err.println("ERROR - " + "lock_type: " + lock.lock_type);
      lock.lock_class = im.getDeclaringClass().toString(); //!!!!
      lock.lock_name = "?????eg phi, Usually local obj? filter it ??"; //Eg, sync(block) in Balancer$Source.getBlockList()J
      return ;
    }
      
    //System.err.println("previous ssa: " + ssas[index]);
    
    //dfsTrackSSAs(ssas[index], lock);
    
    // 3.1 synchronized (ClassName.class from LoadMetadata)   #only two org.apache.hadoop.conf.Configuration.<init>s are not static methods
    if (ssas[index] instanceof SSALoadMetadataInstruction) {
      SSALoadMetadataInstruction loadssa = (SSALoadMetadataInstruction) ssas[index];
      //System.err.println("synchronized (ClassName.class) - " + ssas[index] + " in a static " + im.isStatic() + " method?");
      lock.lock_class = loadssa.getToken().toString();    //previous usage should be wrong: im.getDeclaringClass().toString();
      lock.lock_name = "CLASS"; //((SSALoadMetadataInstruction)ssas[index]).getType().toString();
      //System.err.println("!!!!!!!!!!!!!!!!!!!!!!!!! - synchronized (ClassName.class) - " + functionname + "   class - " + lock.lock_class);
    }
    // 3.2 synchronized (this.object/object from GetField)   #eg, like "v2=getfield<xx..xx>v1"   //whether "getstatic" SSAs like "v2=getstatic<xx..xx>" is involved or not?
    else if (ssas[index] instanceof SSAFieldAccessInstruction) {
      /** WARN - ???
       * funcname: org.apache.hadoop.hdfs.server.balancer.Balancer$Source.dispatchBlocks()V
       * synchronized(Balancer.this) 
       * previous ssa - 41 = getfield < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> > 1
       * lock_name: < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> >
       */               
      SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index];
      lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    //verified: = im.getDeclaringClass().toString(); 
      lock.lock_name = "VARIABLE - GetField- " + fieldssa.getDeclaredField().toString();
    } 
    // 3.3 synchronized (object from a call - Invokexxx + GetField) 
    else if (ssas[index] instanceof SSAInvokeInstruction) {
      SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index];
      if (invokessa.isDispatch()) {      //3.3.1 invokeinterface?/invokevirtual + getfield    #eg, 87 = invokevirtual < Application, Ljava/lang/Process, getInputStream()Ljava/io/InputStream; > 85 @352 exception:86
        int usevn = invokessa.getUse(0); 
        int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from invokevitural)");
        if (index_usevn == -1) { 
          System.err.println("ERROR - sync(object coming from invokevitural) - (index = -1)");
        } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
          System.err.println("ERROR - sync(object coming from invokevitural) - !SSAFieldAccessInstruction");
        } else {
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
          lock.lock_name = "VARIABLE - InvokeVirtual/InvokeInterface+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
        }
      } else if (invokessa.isStatic()) { //3.3.2 invokestatic + getfield    #eg, v27 = invokestatic < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer, access$2000(Lorg/apache/hadoop/hdfs/server/balancer/Balancer;)Ljava/util/Map; > v25 @75 exception:26
        java.util.Set<CGNode> set = cg.getPossibleTargets(function, invokessa.getCallSite());
        if (set.size() == 0) {
          System.err.println("invokessa.getCallSite - " + invokessa.getCallSite());
          System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size = 0 - because the class's SUPERCLASS isn't included in these JarFiles"); // for Test, how to solve the problem??
        }
        if (set.size() >  1) System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size > 1"); // for Test, how to solve the problem??
        if (set.size() > 0) {            //JX: because I haven't yet added "hadoop-common"
          CGNode n = set.iterator().next(); 
          SSAInstruction[] invokessas = n.getIR().getInstructions();
          for (int i=0; i<invokessas.length; i++)                            
            if (invokessas[i] instanceof SSAFieldAccessInstruction) {     //like, a "getField" ssa in Balancer.access$2000
              lock.lock_class = ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().getDeclaringClass().toString();
              lock.lock_name = "VARIABLE - InvokeStatic+GetField- " + ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().toString();
              break;
            }
        }
      } else if (invokessa.isSpecial()) { // 3.3.3 invokespecial?
        lock.lock_class = "????????invokespecial";  //like invokeinterface/invokevirtual?, that is, invokessa.getDeclaredTarget().getDeclaringClass().toString();
        lock.lock_name = "InvokeSpecial- " + invokessa.getDeclaredTarget().toString();
        System.err.println("WARN - SSAInvokeInstruction isSpecial - " + invokessa);
      } else 
        System.err.println("ERROR - other SSAInvokeInstruction? - " + invokessa);
    }
    // 3.4 synchronized (object from CheckCast + InvokeVirtual + GetField)
    else if (ssas[index] instanceof SSACheckCastInstruction) {
      SSACheckCastInstruction checkcastssa = (SSACheckCastInstruction) ssas[index];
      int usevn = checkcastssa.getUse(0); 
      int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from chestcast<+invokevitural>)");
      if (index_usevn == -1) { 
        System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - (index = -1)");
      } else if (!(ssas[index_usevn] instanceof SSAInvokeInstruction)) { 
        System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - !SSAInvokeInstruction");
      } else {
        SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index_usevn];
        int usevn2 = invokessa.getUse(0); 
        int index_usevn2 = getSSAIndexByDefvn(ssas, usevn2, "sync(object coming from <chestcast+>invokevitural)");
        if (index_usevn2 == -1) { 
          System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - (index = -1) -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
        } else if (!(ssas[index_usevn2] instanceof SSAFieldAccessInstruction)) { 
          System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - !SSAFieldAccessInstruction -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
        } else {
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn2];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
          lock.lock_name = "VARIABLE - CheckCast+InvokeVirtual+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
        }
      }
    }
    // 3.5 synchronized (object from ArrayReference + GetField)
    else if (ssas[index] instanceof SSAArrayReferenceInstruction) {
      SSAArrayReferenceInstruction arrayrefssa = (SSAArrayReferenceInstruction) ssas[index];
      int usevn = arrayrefssa.getUse(0); 
      int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object from ArrayReference + GetField)");
      if (index_usevn == -1) { 
        System.err.println("ERROR - sync(object from ArrayReference <+ GetField>) - (index = -1)");
      } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
        System.err.println("ERROR - sync(object from <ArrayReference +> GetField) - !SSAFieldAccessInstruction");
      } else {
        SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
        lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
        lock.lock_name = "VARIABLE - ArrayReference+GetField- " + "ELEMENT" + " in " + fieldssa.getDeclaredField().toString(); //ps-ELEMENT=arrayrefssa.getElementType();  //jx - "getDeclaredTarget" is part of getCallSite
      }
    }
    // 3.6 synchronized (object from New)  must be local object??????
    else if (ssas[index] instanceof SSANewInstruction) {
      //SSANewInstruction newssa = (SSANewInstruction) ssas[index];
      lock.lock_class = im.getDeclaringClass().toString();    
      //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
      int originalindex = getSSAIndexBySSA(ssas, ssa);
      if (originalindex == -1) {
        System.err.println("ERROR - sync(obj from New) - (originalindex = -1)");
        lock.lock_name = "VARIABLE - New- " + "LOCALVAR-???" + " in " + im.getSignature();
      } else {
        lock.lock_name = "VARIABLE - New- " + "LOCALVAR-" + ir.getLocalNames(originalindex, lock.lock_name_vn)[0] + " in " + im.getSignature();  
      }
    }
    // 3.7 other synchronized (xx), that is, other SSAInstructions
    else {
      //TODO - maybe something
      System.err.println("WARN - other SSAInstruction, please have a look - " + ssas[index]);
    }
    
    // Print for single lock if needed
    /*
    System.err.println("funcname: " + functionname);
    System.err.println("ssa: " + ssa);
    //System.err.println("lock_type: " + lock.lock_type);
    System.err.println("lock_class: " + lock.lock_class);
    System.err.println("lock_name: " + lock.lock_name);
    */
  }




====================

// 1. synchronized (this)                       //PS - vn(n>=1) is used for single method, v1=this, v2=par1, v3=par2... ; for static methods, there is not "this", so v1=par1   
    if (lock.lock_name_vn == 1 && !im.isStatic()) { //vn=1 & !im.isStatic, 'this'
      lock.lock_class = im.getDeclaringClass().toString();
      lock.lock_name = "THIS";
      return ;
    } 
    
    // 2. synchronized (argu), agru from method parameters        
    if (!im.isStatic() && lock.lock_name_vn-1 <= ir.getNumberOfParameters()
        || im.isStatic() && lock.lock_name_vn <= ir.getNumberOfParameters()) { //vn in ([par1=this,] par2, par3, par4 ...)  
      int index = getSSAIndexBySSA(ssas, ssa); 
      if (index == -1) {
        System.err.println("ERROR - sync(argu) - (index = -1)");
      } else {
        lock.lock_class = "???????from method parameter, filtered now; actually it should be upward searched to find the fields";  // TODO
        //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
        lock.lock_name = "VARIABLE - ARGU- "+ ir.getLocalNames(index, lock.lock_name_vn)[0];  //should be found for this particular situation  #only for this kind of synchronized_lock now
      }
      return ;
    }
    
    // 3. synchronized(class/object/this.object), not synchronized(xxx.object)    //ie, vn > maxOfParameters, that is, vn is not 'this' and parameters of the method
    int index = getSSAIndexByDefvn(ssas, lock.lock_name_vn, "3.synchronized(class/object/this.object)");;
    if (index == -1) { //phi,pi can't be found in ssas,TODO if needed; Eg, phi like v49 = phi v37,v35, eg, sync(block) in Balancer$Source.getBlockList()J
      System.err.println("ERROR - sync(class/obj/this.obj) - (index = -1) - - SSA:" + ssa);
      //System.err.println("ERROR - " + "funcname: " + functionname);
      //System.err.println("ERROR - " + "ssa: " + ssa);
      //System.err.println("ERROR - " + "lock_type: " + lock.lock_type);
      lock.lock_class = im.getDeclaringClass().toString(); //!!!!
      lock.lock_name = "?????eg phi, Usually local obj? filter it ??"; //Eg, sync(block) in Balancer$Source.getBlockList()J
      return ;
    }
      
    //System.err.println("previous ssa: " + ssas[index]);
    
    //dfsTrackSSAs(ssas[index], lock);
    
    // 3.1 synchronized (ClassName.class from LoadMetadata)   #only two org.apache.hadoop.conf.Configuration.<init>s are not static methods
    if (ssas[index] instanceof SSALoadMetadataInstruction) {
      SSALoadMetadataInstruction loadssa = (SSALoadMetadataInstruction) ssas[index];
      //System.err.println("synchronized (ClassName.class) - " + ssas[index] + " in a static " + im.isStatic() + " method?");
      lock.lock_class = loadssa.getToken().toString();    //previous usage should be wrong: im.getDeclaringClass().toString();
      lock.lock_name = "CLASS"; //((SSALoadMetadataInstruction)ssas[index]).getType().toString();
      //System.err.println("!!!!!!!!!!!!!!!!!!!!!!!!! - synchronized (ClassName.class) - " + functionname + "   class - " + lock.lock_class);
    }
    // 3.2 synchronized (this.object/object from GetField)   #eg, like "v2=getfield<xx..xx>v1"   //whether "getstatic" SSAs like "v2=getstatic<xx..xx>" is involved or not?
    else if (ssas[index] instanceof SSAFieldAccessInstruction) {
      /** WARN - ???
       * funcname: org.apache.hadoop.hdfs.server.balancer.Balancer$Source.dispatchBlocks()V
       * synchronized(Balancer.this) 
       * previous ssa - 41 = getfield < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> > 1
       * lock_name: < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> >
       */               
      SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index];
      lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    //verified: = im.getDeclaringClass().toString(); 
      lock.lock_name = "VARIABLE - GetField- " + fieldssa.getDeclaredField().toString();
    } 
    // 3.3 synchronized (object from a call - Invokexxx + GetField) 
    else if (ssas[index] instanceof SSAInvokeInstruction) {
      SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index];
      if (invokessa.isDispatch()) {      //3.3.1 invokeinterface?/invokevirtual + getfield    #eg, 87 = invokevirtual < Application, Ljava/lang/Process, getInputStream()Ljava/io/InputStream; > 85 @352 exception:86
        int usevn = invokessa.getUse(0); 
        int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from invokevitural)");
        if (index_usevn == -1) { 
          System.err.println("ERROR - sync(object coming from invokevitural) - (index = -1)");
        } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
          System.err.println("ERROR - sync(object coming from invokevitural) - !SSAFieldAccessInstruction");
        } else {
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
          lock.lock_name = "VARIABLE - InvokeVirtual/InvokeInterface+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
        }
      } else if (invokessa.isStatic()) { //3.3.2 invokestatic + getfield    #eg, v27 = invokestatic < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer, access$2000(Lorg/apache/hadoop/hdfs/server/balancer/Balancer;)Ljava/util/Map; > v25 @75 exception:26
        java.util.Set<CGNode> set = cg.getPossibleTargets(function, invokessa.getCallSite());
        if (set.size() == 0) {
          System.err.println("invokessa.getCallSite - " + invokessa.getCallSite());
          System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size = 0 - because the class's SUPERCLASS isn't included in these JarFiles"); // for Test, how to solve the problem??
        }
        if (set.size() >  1) System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size > 1"); // for Test, how to solve the problem??
        if (set.size() > 0) {            //JX: because I haven't yet added "hadoop-common"
          CGNode n = set.iterator().next(); 
          SSAInstruction[] invokessas = n.getIR().getInstructions();
          for (int i=0; i<invokessas.length; i++)                            
            if (invokessas[i] instanceof SSAFieldAccessInstruction) {     //like, a "getField" ssa in Balancer.access$2000
              lock.lock_class = ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().getDeclaringClass().toString();
              lock.lock_name = "VARIABLE - InvokeStatic+GetField- " + ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().toString();
              break;
            }
        }
      } else if (invokessa.isSpecial()) { // 3.3.3 invokespecial?
        lock.lock_class = "????????invokespecial";  //like invokeinterface/invokevirtual?, that is, invokessa.getDeclaredTarget().getDeclaringClass().toString();
        lock.lock_name = "InvokeSpecial- " + invokessa.getDeclaredTarget().toString();
        System.err.println("WARN - SSAInvokeInstruction isSpecial - " + invokessa);
      } else 
        System.err.println("ERROR - other SSAInvokeInstruction? - " + invokessa);
    }
    // 3.4 synchronized (object from CheckCast + InvokeVirtual + GetField)
    else if (ssas[index] instanceof SSACheckCastInstruction) {
      SSACheckCastInstruction checkcastssa = (SSACheckCastInstruction) ssas[index];
      int usevn = checkcastssa.getUse(0); 
      int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from chestcast<+invokevitural>)");
      if (index_usevn == -1) { 
        System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - (index = -1)");
      } else if (!(ssas[index_usevn] instanceof SSAInvokeInstruction)) { 
        System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - !SSAInvokeInstruction");
      } else {
        SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index_usevn];
        int usevn2 = invokessa.getUse(0); 
        int index_usevn2 = getSSAIndexByDefvn(ssas, usevn2, "sync(object coming from <chestcast+>invokevitural)");
        if (index_usevn2 == -1) { 
          System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - (index = -1) -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
        } else if (!(ssas[index_usevn2] instanceof SSAFieldAccessInstruction)) { 
          System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - !SSAFieldAccessInstruction -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
        } else {
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn2];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
          lock.lock_name = "VARIABLE - CheckCast+InvokeVirtual+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
        }
      }
    }
    // 3.5 synchronized (object from ArrayReference + GetField)
    else if (ssas[index] instanceof SSAArrayReferenceInstruction) {
      SSAArrayReferenceInstruction arrayrefssa = (SSAArrayReferenceInstruction) ssas[index];
      int usevn = arrayrefssa.getUse(0); 
      int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object from ArrayReference + GetField)");
      if (index_usevn == -1) { 
        System.err.println("ERROR - sync(object from ArrayReference <+ GetField>) - (index = -1)");
      } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
        System.err.println("ERROR - sync(object from <ArrayReference +> GetField) - !SSAFieldAccessInstruction");
      } else {
        SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
        lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
        lock.lock_name = "VARIABLE - ArrayReference+GetField- " + "ELEMENT" + " in " + fieldssa.getDeclaredField().toString(); //ps-ELEMENT=arrayrefssa.getElementType();  //jx - "getDeclaredTarget" is part of getCallSite
      }
    }
    // 3.6 synchronized (object from New)  must be local object??????
    else if (ssas[index] instanceof SSANewInstruction) {
      //SSANewInstruction newssa = (SSANewInstruction) ssas[index];
      lock.lock_class = im.getDeclaringClass().toString();    
      //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
      int originalindex = getSSAIndexBySSA(ssas, ssa);
      if (originalindex == -1) {
        System.err.println("ERROR - sync(obj from New) - (originalindex = -1)");
        lock.lock_name = "VARIABLE - New- " + "LOCALVAR-???" + " in " + im.getSignature();
      } else {
        lock.lock_name = "VARIABLE - New- " + "LOCALVAR-" + ir.getLocalNames(originalindex, lock.lock_name_vn)[0] + " in " + im.getSignature();  
      }
    }
    // 3.7 other synchronized (xx), that is, other SSAInstructions
    else {
      //TODO - maybe something
      System.err.println("WARN - other SSAInstruction, please have a look - " + ssas[index]);
    }
    
    // Print for single lock if needed
    /*
    System.err.println("funcname: " + functionname);
    System.err.println("ssa: " + ssa);
    //System.err.println("lock_type: " + lock.lock_type);
    System.err.println("lock_class: " + lock.lock_class);
    System.err.println("lock_name: " + lock.lock_name);
    */
  }
  
  ===========================
      
      latest backup
      
   // 3.1 synchronized (ClassName.class from LoadMetadata)   #only two org.apache.hadoop.conf.Configuration.<init>s are not static methods
      if (ssas[index] instanceof SSALoadMetadataInstruction) {
        SSALoadMetadataInstruction loadssa = (SSALoadMetadataInstruction) ssas[index];
        //System.err.println("synchronized (ClassName.class) - " + ssas[index] + " in a static " + im.isStatic() + " method?");
        lock.lock_class = loadssa.getToken().toString();    //previous usage should be wrong: im.getDeclaringClass().toString();
        lock.lock_name = "CLASS"; //((SSALoadMetadataInstruction)ssas[index]).getType().toString();
        //System.err.println("!!!!!!!!!!!!!!!!!!!!!!!!! - synchronized (ClassName.class) - " + functionname + "   class - " + lock.lock_class);
      }
      // 3.2 synchronized (this.object/object from GetField)   #eg, like "v2=getfield<xx..xx>v1"   //whether "getstatic" SSAs like "v2=getstatic<xx..xx>" is involved or not?
      else if (ssas[index] instanceof SSAFieldAccessInstruction) {
        /** WARN - ???
         * funcname: org.apache.hadoop.hdfs.server.balancer.Balancer$Source.dispatchBlocks()V
         * synchronized(Balancer.this) 
         * previous ssa - 41 = getfield < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> > 1
         * lock_name: < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer$Source, this$0, <Application,Lorg/apache/hadoop/hdfs/server/balancer/Balancer> >
         */               
        SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index];
        lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    //verified: = im.getDeclaringClass().toString(); 
        lock.lock_name = "VARIABLE - GetField- " + fieldssa.getDeclaredField().toString();
      } 
      // 3.3 synchronized (object from a call - Invokexxx + GetField) 
      else if (ssas[index] instanceof SSAInvokeInstruction) {
        SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index];
        if (invokessa.isDispatch()) {      //3.3.1 invokeinterface?/invokevirtual + getfield    #eg, 87 = invokevirtual < Application, Ljava/lang/Process, getInputStream()Ljava/io/InputStream; > 85 @352 exception:86
          int usevn = invokessa.getUse(0); 
          int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from invokevitural)");
          if (index_usevn == -1) { 
            System.err.println("ERROR - sync(object coming from invokevitural) - (index = -1)");
          } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
            System.err.println("ERROR - sync(object coming from invokevitural) - !SSAFieldAccessInstruction");
          } else {
            SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
            lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
            lock.lock_name = "VARIABLE - InvokeVirtual/InvokeInterface+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
          }
        } else if (invokessa.isStatic()) { //3.3.2 invokestatic + getfield    #eg, v27 = invokestatic < Application, Lorg/apache/hadoop/hdfs/server/balancer/Balancer, access$2000(Lorg/apache/hadoop/hdfs/server/balancer/Balancer;)Ljava/util/Map; > v25 @75 exception:26
          java.util.Set<CGNode> set = cg.getPossibleTargets(function, invokessa.getCallSite());
          if (set.size() == 0) {
            System.err.println("invokessa.getCallSite - " + invokessa.getCallSite());
            System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size = 0 - because the class's SUPERCLASS isn't included in these JarFiles"); // for Test, how to solve the problem??
          }
          if (set.size() >  1) System.err.println("ERROR - Handling invokestatic - CallGraph#getPossibleTargets's size > 1"); // for Test, how to solve the problem??
          if (set.size() > 0) {            //JX: because I haven't yet added "hadoop-common"
            CGNode n = set.iterator().next(); 
            SSAInstruction[] invokessas = n.getIR().getInstructions();
            for (int i=0; i<invokessas.length; i++)                            
              if (invokessas[i] instanceof SSAFieldAccessInstruction) {     //like, a "getField" ssa in Balancer.access$2000
                lock.lock_class = ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().getDeclaringClass().toString();
                lock.lock_name = "VARIABLE - InvokeStatic+GetField- " + ((SSAFieldAccessInstruction)invokessas[i]).getDeclaredField().toString();
                break;
              }
          }
        } else if (invokessa.isSpecial()) { // 3.3.3 invokespecial?
          lock.lock_class = "????????invokespecial";  //like invokeinterface/invokevirtual?, that is, invokessa.getDeclaredTarget().getDeclaringClass().toString();
          lock.lock_name = "InvokeSpecial- " + invokessa.getDeclaredTarget().toString();
          System.err.println("WARN - SSAInvokeInstruction isSpecial - " + invokessa);
        } else 
          System.err.println("ERROR - other SSAInvokeInstruction? - " + invokessa);
      }
      // 3.4 synchronized (object from CheckCast + InvokeVirtual + GetField)
      else if (ssas[index] instanceof SSACheckCastInstruction) {
        SSACheckCastInstruction checkcastssa = (SSACheckCastInstruction) ssas[index];
        int usevn = checkcastssa.getUse(0); 
        int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object coming from chestcast<+invokevitural>)");
        if (index_usevn == -1) { 
          System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - (index = -1)");
        } else if (!(ssas[index_usevn] instanceof SSAInvokeInstruction)) { 
          System.err.println("ERROR - sync(object coming from chestcast<+invokevitural>) - !SSAInvokeInstruction");
        } else {
          SSAInvokeInstruction invokessa = (SSAInvokeInstruction) ssas[index_usevn];
          int usevn2 = invokessa.getUse(0); 
          int index_usevn2 = getSSAIndexByDefvn(ssas, usevn2, "sync(object coming from <chestcast+>invokevitural)");
          if (index_usevn2 == -1) { 
            System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - (index = -1) -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
          } else if (!(ssas[index_usevn2] instanceof SSAFieldAccessInstruction)) { 
            System.err.println("ERROR - sync(object coming from <chestcast+>invokevitural) - !SSAFieldAccessInstruction -- SSA:" + ssa + " PRESSA:" + ssas[index] + " FUNC:" + lock.functionname);
          } else {
            SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn2];
            lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
            lock.lock_name = "VARIABLE - CheckCast+InvokeVirtual+GetField- " + invokessa.getDeclaredTarget().toString() + " in " + fieldssa.getDeclaredField().toString();  //jx - "getDeclaredTarget" is part of getCallSite
          }
        }
      }
      // 3.5 synchronized (object from ArrayReference + GetField)
      else if (ssas[index] instanceof SSAArrayReferenceInstruction) {
        SSAArrayReferenceInstruction arrayrefssa = (SSAArrayReferenceInstruction) ssas[index];
        int usevn = arrayrefssa.getUse(0); 
        int index_usevn = getSSAIndexByDefvn(ssas, usevn, "sync(object from ArrayReference + GetField)");
        if (index_usevn == -1) { 
          System.err.println("ERROR - sync(object from ArrayReference <+ GetField>) - (index = -1)");
        } else if (!(ssas[index_usevn] instanceof SSAFieldAccessInstruction)) { 
          System.err.println("ERROR - sync(object from <ArrayReference +> GetField) - !SSAFieldAccessInstruction");
        } else {
          SSAFieldAccessInstruction fieldssa = (SSAFieldAccessInstruction) ssas[index_usevn];
          lock.lock_class = fieldssa.getDeclaredField().getDeclaringClass().toString();    
          lock.lock_name = "VARIABLE - ArrayReference+GetField- " + "ELEMENT" + " in " + fieldssa.getDeclaredField().toString(); //ps-ELEMENT=arrayrefssa.getElementType();  //jx - "getDeclaredTarget" is part of getCallSite
        }
      }
      // 3.6 synchronized (object from New)  must be local object??????
      else if (ssas[index] instanceof SSANewInstruction) {
        //SSANewInstruction newssa = (SSANewInstruction) ssas[index];
        lock.lock_class = im.getDeclaringClass().toString();    
        //if (ir.getLocalNames(index, lock.lock_name_vn) != null)
        int originalindex = getSSAIndexBySSA(ssas, ssa);
        if (originalindex == -1) {
          System.err.println("ERROR - sync(obj from New) - (originalindex = -1)");
          lock.lock_name = "VARIABLE - New- " + "LOCALVAR-???" + " in " + im.getSignature();
        } else {
          lock.lock_name = "VARIABLE - New- " + "LOCALVAR-" + ir.getLocalNames(originalindex, lock.lock_name_vn)[0] + " in " + im.getSignature();  
        }
      }
      // 3.7 other synchronized (xx), that is, other SSAInstructions
      else {
        //TODO - maybe something
        System.err.println("WARN - other SSAInstruction, please have a look - " + ssas[index]);
      }
      

      
      
      
      
      