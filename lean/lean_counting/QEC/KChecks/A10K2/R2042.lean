import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8168 = true := by
  decide +kernel

theorem tot8168 : totK PA10K2 A10K2.t8168 = [0, 0, 0, 321051690767, 1501006196313, 2173410006458, 961648458713, 80714234740, 0, 0] := by
  decide +kernel

theorem rows8169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8169 = true := by
  decide +kernel

theorem tot8169 : totK PA10K2 A10K2.t8169 = [0, 0, 0, 0, 601719283770, 2072805600728, 1962077950281, 420186530171, 13242594235, 0] := by
  decide +kernel

theorem rows8170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8170 = true := by
  decide +kernel

theorem tot8170 : totK PA10K2 A10K2.t8170 = [0, 0, 0, 0, 426991915019, 1665335160681, 2018059161404, 737455810555, 61840599361, 0] := by
  decide +kernel

theorem rows8171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8171 = true := by
  decide +kernel

theorem tot8171 : totK PA10K2 A10K2.t8171 = [0, 0, 0, 0, 489769993755, 1860791585269, 2046211928819, 530564148064, 12783470090, 0] := by
  decide +kernel

end QECKChecks.A10K2
