import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7784 = true := by
  decide +kernel

theorem tot7784 : totK PA10K2 A10K2.t7784 = [0, 335055096067, 1240439048725, 1859272931935, 1171265392619, 224805188737, 6356241174, 0, 0, 0] := by
  decide +kernel

theorem rows7785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7785 = true := by
  decide +kernel

theorem tot7785 : totK PA10K2 A10K2.t7785 = [0, 458049624728, 1760656684031, 1989762240829, 685863206377, 31540752808, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7786 = true := by
  decide +kernel

theorem tot7786 : totK PA10K2 A10K2.t7786 = [0, 0, 579070212709, 1881550307780, 1772584348183, 482027376916, 30810868011, 0, 0, 0] := by
  decide +kernel

theorem rows7787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7787 = true := by
  decide +kernel

theorem tot7787 : totK PA10K2 A10K2.t7787 = [0, 471471247616, 1665695240245, 2013796642559, 848391088782, 79130139677, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
