import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6596 = true := by
  decide +kernel

theorem tot6596 : totK PA10K2 A10K2.t6596 = [0, 0, 0, 558305839916, 2019268968612, 1700608506805, 341467679268, 11740596405, 0, 0] := by
  decide +kernel

theorem rows6597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6597 = true := by
  decide +kernel

theorem tot6597 : totK PA10K2 A10K2.t6597 = [0, 0, 0, 460802363259, 1882248959229, 1881033109037, 399049683595, 25336174642, 0, 0] := by
  decide +kernel

theorem rows6598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6598 = true := by
  decide +kernel

theorem tot6598 : totK PA10K2 A10K2.t6598 = [0, 0, 0, 694860922167, 2063208690327, 1583387106164, 296693967273, 11774637377, 0, 0] := by
  decide +kernel

theorem rows6599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6599 = true := by
  decide +kernel

theorem tot6599 : totK PA10K2 A10K2.t6599 = [0, 0, 0, 299483071325, 1514006387403, 2008586974975, 663463076007, 43621830314, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
