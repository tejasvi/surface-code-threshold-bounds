import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7904 = true := by
  decide +kernel

theorem tot7904 : totK PA10K2 A10K2.t7904 = [0, 540969523310, 1904178268321, 2032330355952, 594222853680, 44218942306, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7905 = true := by
  decide +kernel

theorem tot7905 : totK PA10K2 A10K2.t7905 = [0, 0, 715952795547, 2217988179401, 1759981720877, 314477102510, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7906 = true := by
  decide +kernel

theorem tot7906 : totK PA10K2 A10K2.t7906 = [0, 0, 491347330121, 1785493001416, 2131354935424, 744326407375, 56126419230, 0, 0, 0] := by
  decide +kernel

theorem rows7907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7907 = true := by
  decide +kernel

theorem tot7907 : totK PA10K2 A10K2.t7907 = [0, 0, 452578393646, 1771690808642, 1877367546772, 458267700789, 25667075836, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
