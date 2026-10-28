import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5500 = true := by
  decide +kernel

theorem tot5500 : totK PA10K2 A10K2.t5500 = [0, 0, 0, 700523802981, 2072740787024, 1486513686849, 325942154225, 24614390653, 0, 0] := by
  decide +kernel

theorem rows5501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5501 = true := by
  decide +kernel

theorem tot5501 : totK PA10K2 A10K2.t5501 = [0, 0, 419653836988, 1446592588168, 1790381168928, 919910508446, 147197243807, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5502 = true := by
  decide +kernel

theorem tot5502 : totK PA10K2 A10K2.t5502 = [0, 0, 331085228475, 1645867756607, 2152133013965, 715662067881, 40441619481, 0, 0, 0] := by
  decide +kernel

theorem rows5503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5503 = true := by
  decide +kernel

theorem tot5503 : totK PA10K2 A10K2.t5503 = [0, 0, 0, 511346882100, 1846019780137, 1812427541384, 447087878254, 31003444686, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
