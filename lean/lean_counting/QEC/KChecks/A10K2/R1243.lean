import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4972 = true := by
  decide +kernel

theorem tot4972 : totK PA10K2 A10K2.t4972 = [0, 491080547283, 1737442151600, 1923130832699, 637049911906, 57540210985, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4973 = true := by
  decide +kernel

theorem tot4973 : totK PA10K2 A10K2.t4973 = [0, 488504754507, 1873881062787, 1893752001717, 454097569702, 17742097974, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4974 = true := by
  decide +kernel

theorem tot4974 : totK PA10K2 A10K2.t4974 = [0, 0, 570483013807, 1972147757374, 1656474534882, 399605066241, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows4975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4975 = true := by
  decide +kernel

theorem tot4975 : totK PA10K2 A10K2.t4975 = [0, 325086607341, 1294674534072, 1869668920892, 1031400628596, 169113136228, 5410721913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
