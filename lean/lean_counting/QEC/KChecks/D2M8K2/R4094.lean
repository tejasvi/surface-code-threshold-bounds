import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16376 = true := by
  decide +kernel

theorem tot16376 : totK PD2M8K2 D2M8K2.t16376 = [0, 0, 0, 206648400236, 478376090041, 199603370423, 11433198393, 0] := by
  decide +kernel

theorem rows16377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16377 = true := by
  decide +kernel

theorem tot16377 : totK PD2M8K2 D2M8K2.t16377 = [0, 0, 0, 173218806183, 466406879198, 224639041927, 11335667594, 0] := by
  decide +kernel

theorem rows16378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16378 = true := by
  decide +kernel

theorem tot16378 : totK PD2M8K2 D2M8K2.t16378 = [0, 0, 0, 0, 277781525978, 476293550427, 92228046928, 1086231185] := by
  decide +kernel

theorem rows16379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16379 = true := by
  decide +kernel

theorem tot16379 : totK PD2M8K2 D2M8K2.t16379 = [0, 0, 0, 105964568707, 377244338246, 305824481630, 73179864298, 3752012233] := by
  decide +kernel

end QECKChecks.D2M8K2
