import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5724 = true := by
  decide +kernel

theorem tot5724 : totK PA10K2 A10K2.t5724 = [0, 0, 88901432086, 843926011713, 1969068135115, 1399759707255, 317807742970, 25565504801, 0, 0] := by
  decide +kernel

theorem rows5725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5725 = true := by
  decide +kernel

theorem tot5725 : totK PA10K2 A10K2.t5725 = [0, 0, 202308092638, 1130328286194, 1979351492229, 1192029148154, 189627045438, 5517381808, 0, 0] := by
  decide +kernel

theorem rows5726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5726 = true := by
  decide +kernel

theorem tot5726 : totK PA10K2 A10K2.t5726 = [0, 0, 584263778251, 1864427164933, 1776763880506, 499021892836, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows5727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5727 = true := by
  decide +kernel

theorem tot5727 : totK PA10K2 A10K2.t5727 = [0, 0, 0, 1060387972403, 2475590713835, 1079466621361, 77355190755, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
