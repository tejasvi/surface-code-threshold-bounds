import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2084 = true := by
  decide +kernel

theorem tot2084 : totK PA10K2 A10K2.t2084 = [0, 0, 546278226073, 1955628088524, 1872094468484, 423256733868, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows2085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2085 = true := by
  decide +kernel

theorem tot2085 : totK PA10K2 A10K2.t2085 = [0, 0, 0, 565976477168, 1954987850335, 1668322489945, 405999952804, 25565504801, 0, 0] := by
  decide +kernel

theorem rows2086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2086 = true := by
  decide +kernel

theorem tot2086 : totK PA10K2 A10K2.t2086 = [0, 0, 436150433304, 1536309260717, 1715438885443, 792956881445, 147617656792, 5453062850, 0, 0] := by
  decide +kernel

theorem rows2087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2087 = true := by
  decide +kernel

theorem tot2087 : totK PA10K2 A10K2.t2087 = [0, 0, 279666710650, 1514927969501, 2073256060184, 657568123154, 38673136708, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
