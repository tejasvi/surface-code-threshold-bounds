import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10192 = true := by
  decide +kernel

theorem tot10192 : totK PD2M8K2 D2M8K2.t10192 = [0, 123585036299, 276922653984, 156738914587, 199755664944, 127485466193, 11893557120, 0] := by
  decide +kernel

theorem rows10193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10193 = true := by
  decide +kernel

theorem tot10193 : totK PD2M8K2 D2M8K2.t10193 = [0, 184632674499, 457717850342, 232505877920, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows10194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10194 = true := by
  decide +kernel

theorem tot10194 : totK PD2M8K2 D2M8K2.t10194 = [0, 124655673597, 435183632919, 312545230788, 28504154241, 0, 0, 0] := by
  decide +kernel

theorem rows10195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10195 = true := by
  decide +kernel

theorem tot10195 : totK PD2M8K2 D2M8K2.t10195 = [0, 0, 275123105893, 508299202397, 109865622811, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
