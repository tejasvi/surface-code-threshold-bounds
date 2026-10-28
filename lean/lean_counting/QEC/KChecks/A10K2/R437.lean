import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1748 = true := by
  decide +kernel

theorem tot1748 : totK PA10K2 A10K2.t1748 = [0, 0, 188738831720, 965367390309, 1989949224129, 1356329513686, 212777463919, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1749 = true := by
  decide +kernel

theorem tot1749 : totK PA10K2 A10K2.t1749 = [0, 0, 406654396340, 1794923834336, 2207880975177, 685557680021, 33234847578, 0, 0, 0] := by
  decide +kernel

theorem rows1750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1750 = true := by
  decide +kernel

theorem tot1750 : totK PA10K2 A10K2.t1750 = [0, 0, 0, 593371642305, 2134130484054, 2004171916290, 388972205863, 6962742351, 0, 0] := by
  decide +kernel

theorem rows1751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1751 = true := by
  decide +kernel

theorem tot1751 : totK PA10K2 A10K2.t1751 = [0, 0, 557584295228, 1817390681601, 1709540265499, 604222486995, 105543107864, 5963379153, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
