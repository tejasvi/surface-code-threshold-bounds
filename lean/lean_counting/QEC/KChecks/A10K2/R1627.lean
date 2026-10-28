import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6508 = true := by
  decide +kernel

theorem tot6508 : totK PA10K2 A10K2.t6508 = [0, 227459092167, 1265901841392, 2204364439575, 1241715938646, 135257236659, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6509 = true := by
  decide +kernel

theorem tot6509 : totK PA10K2 A10K2.t6509 = [0, 94186449629, 709351946221, 1834234426215, 1703621157826, 470677593212, 31747192500, 0, 0, 0] := by
  decide +kernel

theorem rows6510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6510 = true := by
  decide +kernel

theorem tot6510 : totK PA10K2 A10K2.t6510 = [0, 524196523564, 1909695692130, 2025551126647, 587471039602, 37831916145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6511 = true := by
  decide +kernel

theorem tot6511 : totK PA10K2 A10K2.t6511 = [0, 227811217789, 1223828125554, 2085580130500, 1222658405941, 207192424225, 6586990447, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
