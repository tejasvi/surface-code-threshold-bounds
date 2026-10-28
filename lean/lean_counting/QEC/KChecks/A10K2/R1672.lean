import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6688 = true := by
  decide +kernel

theorem tot6688 : totK PA10K2 A10K2.t6688 = [0, 504850548399, 1850502268034, 2069741300074, 651712987543, 39353282504, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6689 = true := by
  decide +kernel

theorem tot6689 : totK PA10K2 A10K2.t6689 = [0, 0, 718695477975, 2187331753228, 1810106038326, 323831189494, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows6690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6690 = true := by
  decide +kernel

theorem tot6690 : totK PA10K2 A10K2.t6690 = [0, 0, 601623009361, 2034491713007, 1835423529026, 455875723050, 28177825909, 0, 0, 0] := by
  decide +kernel

theorem rows6691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6691 = true := by
  decide +kernel

theorem tot6691 : totK PA10K2 A10K2.t6691 = [0, 0, 521530066387, 1787909649684, 1797729867617, 474977488571, 31222411477, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
