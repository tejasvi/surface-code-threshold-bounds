import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4980 = true := by
  decide +kernel

theorem tot4980 : totK PA10K2 A10K2.t4980 = [171047095287, 1050169312612, 1959229133484, 1278847482837, 276016399436, 20340910120, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4981 = true := by
  decide +kernel

theorem tot4981 : totK PA10K2 A10K2.t4981 = [137276975699, 807142085811, 1860594985394, 1602623891580, 333250296694, 11427838733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4982 = true := by
  decide +kernel

theorem tot4982 : totK PA10K2 A10K2.t4982 = [452698645285, 1690215774502, 1929605022113, 666433568168, 52230029129, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4983 = true := by
  decide +kernel

theorem tot4983 : totK PA10K2 A10K2.t4983 = [184193489587, 1383060026110, 2252750378007, 952392162504, 67340780067, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
