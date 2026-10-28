import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2068 = true := by
  decide +kernel

theorem tot2068 : totK PA10K2 A10K2.t2068 = [0, 312057137912, 1300685328499, 2008830680438, 1196776761069, 222598571347, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows2069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2069 = true := by
  decide +kernel

theorem tot2069 : totK PA10K2 A10K2.t2069 = [0, 505017398559, 1849825456260, 1980944469048, 569589917799, 31947994545, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2070 = true := by
  decide +kernel

theorem tot2070 : totK PA10K2 A10K2.t2070 = [0, 0, 782056159807, 2226575017332, 1641271302897, 277346818151, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows2071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2071 = true := by
  decide +kernel

theorem tot2071 : totK PA10K2 A10K2.t2071 = [0, 512905690969, 1721723390680, 1884260462144, 761244047811, 66625263491, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
