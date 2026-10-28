import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4384 = true := by
  decide +kernel

theorem tot4384 : totK PA10K2 A10K2.t4384 = [0, 180626633693, 954886273454, 1891561226681, 1385867564379, 346157138107, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4385 = true := by
  decide +kernel

theorem tot4385 : totK PA10K2 A10K2.t4385 = [0, 263847796660, 1085496216896, 1879520836697, 1331724764232, 225551691074, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows4386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4386 = true := by
  decide +kernel

theorem tot4386 : totK PA10K2 A10K2.t4386 = [0, 390517805825, 1753202772371, 2096009319395, 609941759782, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4387 = true := by
  decide +kernel

theorem tot4387 : totK PA10K2 A10K2.t4387 = [0, 0, 556089254569, 2004538552638, 1787474305928, 366745336161, 25299471099, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
