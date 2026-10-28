import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2908 = true := by
  decide +kernel

theorem tot2908 : totK PA10K2 A10K2.t2908 = [0, 510058576851, 1868354248328, 2006638050447, 549413326735, 12917769548, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2909 = true := by
  decide +kernel

theorem tot2909 : totK PA10K2 A10K2.t2909 = [0, 0, 515977741285, 1875187979557, 1781455631769, 435727394552, 25565504801, 0, 0, 0] := by
  decide +kernel

theorem rows2910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2910 = true := by
  decide +kernel

theorem tot2910 : totK PA10K2 A10K2.t2910 = [0, 382064625605, 1548149347308, 1936225701964, 904778883810, 145165710797, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows2911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2911 = true := by
  decide +kernel

theorem tot2911 : totK PA10K2 A10K2.t2911 = [0, 183095495758, 1086804732236, 2072059338491, 1203870481796, 190455277787, 6121173289, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
