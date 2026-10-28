import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4568 = true := by
  decide +kernel

theorem tot4568 : totK PA10K2 A10K2.t4568 = [0, 120208617333, 929782085234, 1958860050597, 1469130168347, 367493944841, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4569 = true := by
  decide +kernel

theorem tot4569 : totK PA10K2 A10K2.t4569 = [0, 276491011440, 1188244694543, 1912473327904, 1230419991788, 200403563315, 5447185874, 0, 0, 0] := by
  decide +kernel

theorem rows4570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4570 = true := by
  decide +kernel

theorem tot4570 : totK PA10K2 A10K2.t4570 = [0, 500180958923, 1748138926300, 1856799621919, 611120919186, 51464731716, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4571 = true := by
  decide +kernel

theorem tot4571 : totK PA10K2 A10K2.t4571 = [0, 0, 1012235294946, 2438849396382, 1195136112569, 106280156807, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
