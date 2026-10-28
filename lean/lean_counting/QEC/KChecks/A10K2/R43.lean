import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t172 = true := by
  decide +kernel

theorem tot172 : totK PA10K2 A10K2.t172 = [226625864075, 1219311326433, 2152775459284, 1278483663168, 178067811384, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t173 = true := by
  decide +kernel

theorem tot173 : totK PA10K2 A10K2.t173 = [0, 588944299074, 2040304616844, 1921416508372, 399538996800, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t174 = true := by
  decide +kernel

theorem tot174 : totK PA10K2 A10K2.t174 = [0, 401834156581, 1577193930310, 2015477162453, 820986361309, 74643347679, 0, 0, 0, 0] := by
  decide +kernel

theorem rows175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t175 = true := by
  decide +kernel

theorem tot175 : totK PA10K2 A10K2.t175 = [0, 379078713572, 1663792793428, 2127283344414, 765574950807, 56090844725, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
