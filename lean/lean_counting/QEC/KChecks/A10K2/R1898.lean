import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7592 = true := by
  decide +kernel

theorem tot7592 : totK PA10K2 A10K2.t7592 = [0, 0, 165887444701, 1123882922446, 2128463347174, 1331740978618, 204044680173, 6066958478, 0, 0] := by
  decide +kernel

theorem rows7593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7593 = true := by
  decide +kernel

theorem tot7593 : totK PA10K2 A10K2.t7593 = [0, 0, 0, 604864684323, 2036777659680, 1926611723072, 405878342633, 11910457242, 0, 0] := by
  decide +kernel

theorem rows7594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7594 = true := by
  decide +kernel

theorem tot7594 : totK PA10K2 A10K2.t7594 = [0, 0, 480093498052, 1478118058683, 1600326314426, 935637042489, 370458374545, 43132710386, 0, 0] := by
  decide +kernel

theorem rows7595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7595 = true := by
  decide +kernel

theorem tot7595 : totK PA10K2 A10K2.t7595 = [0, 0, 296016977241, 1570691660900, 2201082925700, 882090125089, 76569353717, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
