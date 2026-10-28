import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4748 = true := by
  decide +kernel

theorem tot4748 : totK PA10K2 A10K2.t4748 = [0, 0, 0, 618156211046, 2021657818866, 1645995993675, 392671250849, 25565504801, 0, 0] := by
  decide +kernel

theorem rows4749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4749 = true := by
  decide +kernel

theorem tot4749 : totK PA10K2 A10K2.t4749 = [0, 0, 400871179982, 1458270749399, 1760576967787, 950227934202, 172502972979, 5517381808, 0, 0] := by
  decide +kernel

theorem rows4750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4750 = true := by
  decide +kernel

theorem tot4750 : totK PA10K2 A10K2.t4750 = [0, 0, 369669781866, 1668954761019, 2078965758991, 609022399697, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows4751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4751 = true := by
  decide +kernel

theorem tot4751 : totK PA10K2 A10K2.t4751 = [0, 0, 72405881961, 774138031094, 2090644863600, 1426682799006, 213007971328, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
