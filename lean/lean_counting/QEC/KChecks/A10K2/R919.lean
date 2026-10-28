import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3676 = true := by
  decide +kernel

theorem tot3676 : totK PA10K2 A10K2.t3676 = [0, 0, 605061847711, 1996597819595, 1959069318326, 537918965142, 27903531280, 0, 0, 0] := by
  decide +kernel

theorem rows3677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3677 = true := by
  decide +kernel

theorem tot3677 : totK PA10K2 A10K2.t3677 = [0, 0, 0, 899496008740, 2499859564273, 1626077980366, 182671518811, 0, 0, 0] := by
  decide +kernel

theorem rows3678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3678 = true := by
  decide +kernel

theorem tot3678 : totK PA10K2 A10K2.t3678 = [0, 156758555584, 351946453192, 502360600314, 1454081317852, 1895731043578, 671356004017, 42874818239, 0, 0] := by
  decide +kernel

theorem rows3679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3679 = true := by
  decide +kernel

theorem tot3679 : totK PA10K2 A10K2.t3679 = [0, 416499976062, 1733929005885, 1962812103751, 534413003436, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
