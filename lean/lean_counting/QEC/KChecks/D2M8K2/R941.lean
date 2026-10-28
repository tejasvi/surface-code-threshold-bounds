import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3764 = true := by
  decide +kernel

theorem tot3764 : totK PD2M8K2 D2M8K2.t3764 = [0, 177643195629, 452113182885, 260159859765, 25356230767, 0, 0, 0] := by
  decide +kernel

theorem rows3765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3765 = true := by
  decide +kernel

theorem tot3765 : totK PD2M8K2 D2M8K2.t3765 = [0, 167909905344, 485430353745, 240962556399, 7775175011, 0, 0, 0] := by
  decide +kernel

theorem rows3766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3766 = true := by
  decide +kernel

theorem tot3766 : totK PD2M8K2 D2M8K2.t3766 = [173418262769, 444660364785, 245913579118, 41380624741, 4429463114, 0, 0, 0] := by
  decide +kernel

theorem rows3767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3767 = true := by
  decide +kernel

theorem tot3767 : totK PD2M8K2 D2M8K2.t3767 = [193130350898, 467202472944, 224280507178, 15617333555, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
