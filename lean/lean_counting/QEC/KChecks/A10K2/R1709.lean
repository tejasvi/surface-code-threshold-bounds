import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6836 = true := by
  decide +kernel

theorem tot6836 : totK PA10K2 A10K2.t6836 = [0, 0, 744758057999, 2224381158733, 1749984885359, 307433735571, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6837 = true := by
  decide +kernel

theorem tot6837 : totK PA10K2 A10K2.t6837 = [0, 0, 503652345274, 1788771165764, 2081542354451, 721092439505, 55498468803, 0, 0, 0] := by
  decide +kernel

theorem rows6838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6838 = true := by
  decide +kernel

theorem tot6838 : totK PA10K2 A10K2.t6838 = [0, 0, 424280604323, 1708657847026, 1882430332652, 509840204995, 31112697984, 0, 0, 0] := by
  decide +kernel

theorem rows6839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6839 = true := by
  decide +kernel

theorem tot6839 : totK PA10K2 A10K2.t6839 = [0, 0, 280606888742, 1380259858661, 2120306731248, 1076974550187, 130888576776, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
