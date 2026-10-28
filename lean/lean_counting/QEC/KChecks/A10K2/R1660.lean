import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6640 = true := by
  decide +kernel

theorem tot6640 : totK PA10K2 A10K2.t6640 = [0, 0, 330021797788, 1549771858633, 2191348771602, 873559926129, 62972848401, 0, 0, 0] := by
  decide +kernel

theorem rows6641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6641 = true := by
  decide +kernel

theorem tot6641 : totK PA10K2 A10K2.t6641 = [0, 0, 0, 605929553522, 2006148625731, 1864813914912, 394224561704, 12224107035, 0, 0] := by
  decide +kernel

theorem rows6642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6642 = true := by
  decide +kernel

theorem tot6642 : totK PA10K2 A10K2.t6642 = [319295482399, 864280957511, 535681983599, 287332845721, 1032839242216, 1347230720856, 522441368230, 48886019071, 0, 0] := by
  decide +kernel

theorem rows6643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6643 = true := by
  decide +kernel

theorem tot6643 : totK PA10K2 A10K2.t6643 = [510631144184, 1757168551135, 1841166359529, 521596735879, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
