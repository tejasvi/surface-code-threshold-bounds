import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6304 = true := by
  decide +kernel

theorem tot6304 : totK PD2M8K2 D2M8K2.t6304 = [0, 155746706840, 458874210139, 268800306956, 18883739269, 0, 0, 0] := by
  decide +kernel

theorem rows6305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6305 = true := by
  decide +kernel

theorem tot6305 : totK PD2M8K2 D2M8K2.t6305 = [0, 0, 269680581945, 508626153600, 110385960121, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6306 = true := by
  decide +kernel

theorem tot6306 : totK PD2M8K2 D2M8K2.t6306 = [0, 156388264978, 438704000936, 290449940612, 27660565543, 0, 0, 0] := by
  decide +kernel

theorem rows6307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6307 = true := by
  decide +kernel

theorem tot6307 : totK PD2M8K2 D2M8K2.t6307 = [0, 181276880681, 445143101161, 256755979157, 23494672053, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
