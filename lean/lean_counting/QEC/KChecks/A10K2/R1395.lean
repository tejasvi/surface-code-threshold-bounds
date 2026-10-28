import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5580 = true := by
  decide +kernel

theorem tot5580 : totK PA10K2 A10K2.t5580 = [0, 433354746640, 1779330930638, 1974727979474, 603550281311, 41201510957, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5581 = true := by
  decide +kernel

theorem tot5581 : totK PA10K2 A10K2.t5581 = [0, 0, 481300927325, 1940443781400, 1838765341055, 421947683502, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5582 = true := by
  decide +kernel

theorem tot5582 : totK PA10K2 A10K2.t5582 = [0, 450753985084, 1589706921097, 1807955655586, 830724556083, 145282594102, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5583 = true := by
  decide +kernel

theorem tot5583 : totK PA10K2 A10K2.t5583 = [0, 107692589913, 981831504550, 1985087191769, 1308195868668, 329850252169, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
