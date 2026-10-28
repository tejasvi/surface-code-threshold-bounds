import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t312 = true := by
  decide +kernel

theorem tot312 : totK PA10K2 A10K2.t312 = [0, 268742465433, 1445576704820, 2183092998512, 853256700862, 60081521450, 0, 0, 0, 0] := by
  decide +kernel

theorem rows313 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t313 = true := by
  decide +kernel

theorem tot313 : totK PA10K2 A10K2.t313 = [0, 203500214571, 766408453601, 1557493547425, 1691991489100, 493510459406, 31768748853, 0, 0, 0] := by
  decide +kernel

theorem rows314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t314 = true := by
  decide +kernel

theorem tot314 : totK PA10K2 A10K2.t314 = [0, 486058922395, 1670788572664, 1878412809253, 617900730134, 51800411270, 0, 0, 0, 0] := by
  decide +kernel

theorem rows315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t315 = true := by
  decide +kernel

theorem tot315 : totK PA10K2 A10K2.t315 = [0, 49099161495, 1132734546456, 2333810574037, 1110232494565, 100760845431, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
