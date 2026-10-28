import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1812 = true := by
  decide +kernel

theorem tot1812 : totK PA10K2 A10K2.t1812 = [0, 0, 0, 443967750433, 1765345410640, 1933949807927, 528634013117, 32040661968, 0, 0] := by
  decide +kernel

theorem rows1813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1813 = true := by
  decide +kernel

theorem tot1813 : totK PA10K2 A10K2.t1813 = [0, 0, 0, 84840571019, 883005752969, 1961712741701, 1277144920474, 300721606438, 24614390653, 0] := by
  decide +kernel

theorem rows1814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1814 = true := by
  decide +kernel

theorem tot1814 : totK PA10K2 A10K2.t1814 = [0, 0, 0, 280069521284, 1248811504328, 1935435505400, 1024054943975, 168461462814, 5460492893, 0] := by
  decide +kernel

theorem rows1815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1815 = true := by
  decide +kernel

theorem tot1815 : totK PA10K2 A10K2.t1815 = [0, 0, 0, 414155314625, 1714284728506, 2053937949808, 550227310479, 33590035193, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
