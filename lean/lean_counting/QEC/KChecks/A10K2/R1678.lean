import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6712 = true := by
  decide +kernel

theorem tot6712 : totK PA10K2 A10K2.t6712 = [0, 0, 577834453103, 2038281308116, 1964073496267, 437952224352, 12270510475, 0, 0, 0] := by
  decide +kernel

theorem rows6713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6713 = true := by
  decide +kernel

theorem tot6713 : totK PA10K2 A10K2.t6713 = [466373786949, 1555833620937, 1516885703209, 544071236630, 429598630286, 308839707511, 43244704466, 0, 0, 0] := by
  decide +kernel

theorem rows6714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6714 = true := by
  decide +kernel

theorem tot6714 : totK PA10K2 A10K2.t6714 = [370539782661, 1673978549416, 2056465086673, 715643377417, 55861130137, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6715 = true := by
  decide +kernel

theorem tot6715 : totK PA10K2 A10K2.t6715 = [0, 437691317779, 1825637236274, 1889894956595, 448219504399, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
