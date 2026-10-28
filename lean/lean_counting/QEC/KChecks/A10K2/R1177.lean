import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4708 = true := by
  decide +kernel

theorem tot4708 : totK PA10K2 A10K2.t4708 = [0, 0, 0, 277817397023, 1524244299235, 2052128679325, 637386625579, 38414300562, 0, 0] := by
  decide +kernel

theorem rows4709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4709 = true := by
  decide +kernel

theorem tot4709 : totK PA10K2 A10K2.t4709 = [0, 0, 0, 254973889144, 1087880067410, 1878635935729, 1156756707732, 185540164104, 5685526223, 0] := by
  decide +kernel

theorem rows4710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4710 = true := by
  decide +kernel

theorem tot4710 : totK PA10K2 A10K2.t4710 = [0, 0, 0, 481997670728, 1895968859729, 2032648365286, 523303381737, 27915140041, 0, 0] := by
  decide +kernel

theorem rows4711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4711 = true := by
  decide +kernel

theorem tot4711 : totK PA10K2 A10K2.t4711 = [0, 0, 468537272203, 1793766635933, 1893693323382, 492381851961, 65620422312, 17004268500, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
