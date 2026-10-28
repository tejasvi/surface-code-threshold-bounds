import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3868 = true := by
  decide +kernel

theorem tot3868 : totK PD2M8K2 D2M8K2.t3868 = [0, 185751082966, 470044939815, 222032123574, 13676273063, 0, 0, 0] := by
  decide +kernel

theorem rows3869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3869 = true := by
  decide +kernel

theorem tot3869 : totK PD2M8K2 D2M8K2.t3869 = [0, 0, 287369566025, 503649100942, 105313592406, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3870 = true := by
  decide +kernel

theorem tot3870 : totK PD2M8K2 D2M8K2.t3870 = [0, 85618013281, 382101715699, 383230610615, 46501969767, 0, 0, 0] := by
  decide +kernel

theorem rows3871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3871 = true := by
  decide +kernel

theorem tot3871 : totK PD2M8K2 D2M8K2.t3871 = [0, 167661689259, 440319284351, 266254548432, 26841706846, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
