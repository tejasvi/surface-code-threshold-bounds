import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t700 = true := by
  decide +kernel

theorem tot700 : totK PA10K2 A10K2.t700 = [0, 0, 148546679657, 1035779365706, 2002094587379, 1234052594435, 277251570241, 24941563133, 0, 0] := by
  decide +kernel

theorem rows701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t701 = true := by
  decide +kernel

theorem tot701 : totK PA10K2 A10K2.t701 = [0, 0, 283653827384, 1235153200097, 1906486396602, 1096207295713, 169107924958, 5447185874, 0, 0] := by
  decide +kernel

theorem rows702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t702 = true := by
  decide +kernel

theorem tot702 : totK PA10K2 A10K2.t702 = [0, 0, 491260763279, 1689124378067, 1845800187866, 612392545767, 51464731716, 0, 0, 0] := by
  decide +kernel

theorem rows703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t703 = true := by
  decide +kernel

theorem tot703 : totK PA10K2 A10K2.t703 = [0, 0, 0, 1049359668419, 2412277695636, 1120387513682, 105828952891, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
