import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4356 = true := by
  decide +kernel

theorem tot4356 : totK PA10K2 A10K2.t4356 = [0, 0, 479734269350, 1770749436726, 2056356598609, 732032286934, 59650435174, 0, 0, 0] := by
  decide +kernel

theorem rows4357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4357 = true := by
  decide +kernel

theorem tot4357 : totK PA10K2 A10K2.t4357 = [0, 0, 317566478666, 1504628725334, 2140612861817, 857787571630, 71232245326, 0, 0, 0] := by
  decide +kernel

theorem rows4358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4358 = true := by
  decide +kernel

theorem tot4358 : totK PA10K2 A10K2.t4358 = [0, 0, 0, 549213864838, 2012109560489, 2029041139236, 505850258208, 18381869251, 0, 0] := by
  decide +kernel

theorem rows4359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4359 = true := by
  decide +kernel

theorem tot4359 : totK PA10K2 A10K2.t4359 = [0, 583356039855, 1934648030866, 1768126460585, 428306803685, 55006505703, 54517668636, 17121492619, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
