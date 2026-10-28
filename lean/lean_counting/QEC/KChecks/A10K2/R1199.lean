import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4796 = true := by
  decide +kernel

theorem tot4796 : totK PA10K2 A10K2.t4796 = [0, 39431801073, 1009733335032, 2325895640456, 1215735313205, 105794386408, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4797 = true := by
  decide +kernel

theorem tot4797 : totK PA10K2 A10K2.t4797 = [0, 487223217921, 1779246333542, 1921806763510, 711500120626, 129018254905, 5982052406, 0, 0, 0] := by
  decide +kernel

theorem rows4798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4798 = true := by
  decide +kernel

theorem tot4798 : totK PA10K2 A10K2.t4798 = [0, 316779408161, 1355738300722, 2087210411631, 1169437675252, 201363108990, 6585347165, 0, 0, 0] := by
  decide +kernel

theorem rows4799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4799 = true := by
  decide +kernel

theorem tot4799 : totK PA10K2 A10K2.t4799 = [0, 0, 611006629396, 2085693664790, 1952410355257, 409429583392, 6962742351, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
