import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4724 = true := by
  decide +kernel

theorem tot4724 : totK PA10K2 A10K2.t4724 = [0, 0, 498031759301, 1863419743344, 2008141569234, 545235869214, 12587195483, 0, 0, 0] := by
  decide +kernel

theorem rows4725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4725 = true := by
  decide +kernel

theorem tot4725 : totK PA10K2 A10K2.t4725 = [0, 0, 0, 687476523495, 2083853956972, 1687509118623, 402486546997, 25660650750, 0, 0] := by
  decide +kernel

theorem rows4726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4726 = true := by
  decide +kernel

theorem tot4726 : totK PA10K2 A10K2.t4726 = [0, 0, 480704820675, 1750163586906, 2030041132221, 810575952407, 83121000041, 0, 0, 0] := by
  decide +kernel

theorem rows4727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4727 = true := by
  decide +kernel

theorem tot4727 : totK PA10K2 A10K2.t4727 = [0, 0, 317795168379, 1538981054590, 2174809101740, 908406035896, 90044888563, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
