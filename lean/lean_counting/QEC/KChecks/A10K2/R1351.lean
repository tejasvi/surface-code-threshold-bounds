import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5404 = true := by
  decide +kernel

theorem tot5404 : totK PA10K2 A10K2.t5404 = [0, 46039240014, 949351834505, 2256391318765, 1552396107727, 271408747171, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5405 = true := by
  decide +kernel

theorem tot5405 : totK PA10K2 A10K2.t5405 = [0, 0, 400731750356, 1726781012309, 2137129787634, 707171923311, 30131324859, 0, 0, 0] := by
  decide +kernel

theorem rows5406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5406 = true := by
  decide +kernel

theorem tot5406 : totK PA10K2 A10K2.t5406 = [0, 0, 395950443332, 1519850485409, 2025468956302, 1039218751948, 128812558380, 0, 0, 0] := by
  decide +kernel

theorem rows5407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5407 = true := by
  decide +kernel

theorem tot5407 : totK PA10K2 A10K2.t5407 = [0, 0, 468624519169, 1827567679288, 1967216439154, 550196389657, 31947994545, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
