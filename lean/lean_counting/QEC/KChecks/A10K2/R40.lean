import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t160 = true := by
  decide +kernel

theorem tot160 : totK PA10K2 A10K2.t160 = [121146523123, 1045814516067, 2213632048667, 1488473615814, 276486577572, 6851704726, 0, 0, 0, 0] := by
  decide +kernel

theorem rows161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t161 = true := by
  decide +kernel

theorem tot161 : totK PA10K2 A10K2.t161 = [0, 466772010805, 1883852767005, 2141433964436, 570985079145, 18813240752, 0, 0, 0, 0] := by
  decide +kernel

theorem rows162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t162 = true := by
  decide +kernel

theorem tot162 : totK PA10K2 A10K2.t162 = [0, 592988321650, 1915943386261, 1867641240537, 622961778728, 63792639202, 0, 0, 0, 0] := by
  decide +kernel

theorem rows163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t163 = true := by
  decide +kernel

theorem tot163 : totK PA10K2 A10K2.t163 = [0, 0, 733609987177, 2144181551720, 1640022065732, 375961559672, 25565504801, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
