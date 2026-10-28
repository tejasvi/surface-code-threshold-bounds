import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4548 = true := by
  decide +kernel

theorem tot4548 : totK PA10K2 A10K2.t4548 = [0, 0, 619903949224, 2001228599524, 1661847113900, 391391875839, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows4549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4549 = true := by
  decide +kernel

theorem tot4549 : totK PA10K2 A10K2.t4549 = [0, 400871179982, 1397477253252, 1773295010142, 998114472885, 178995699509, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows4550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4550 = true := by
  decide +kernel

theorem tot4550 : totK PA10K2 A10K2.t4550 = [0, 369669781866, 1717388446199, 2062256963019, 587369348262, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4551 = true := by
  decide +kernel

theorem tot4551 : totK PA10K2 A10K2.t4551 = [0, 42431094195, 723030158645, 2152871311425, 1470533927922, 213007971328, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
