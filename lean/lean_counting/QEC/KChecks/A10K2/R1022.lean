import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4088 = true := by
  decide +kernel

theorem tot4088 : totK PA10K2 A10K2.t4088 = [546777004572, 1813573645891, 1834625609265, 664980745465, 131708244873, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4089 = true := by
  decide +kernel

theorem tot4089 : totK PA10K2 A10K2.t4089 = [194767307979, 1201777139954, 2155121823523, 1184965561773, 135097953177, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4090 = true := by
  decide +kernel

theorem tot4090 : totK PA10K2 A10K2.t4090 = [0, 440187277161, 1752881700315, 2080507207855, 574267687614, 17951502659, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4091 = true := by
  decide +kernel

theorem tot4091 : totK PA10K2 A10K2.t4091 = [0, 580426818031, 1856879916680, 1772367589135, 594564678031, 62956601428, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
