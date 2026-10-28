import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3680 = true := by
  decide +kernel

theorem tot3680 : totK PA10K2 A10K2.t3680 = [0, 187747219659, 987912831060, 1876203632335, 1404285787994, 354756311970, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows3681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3681 = true := by
  decide +kernel

theorem tot3681 : totK PA10K2 A10K2.t3681 = [0, 278580461261, 1168244179250, 1848982373102, 1267752663172, 218751712457, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows3682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3682 = true := by
  decide +kernel

theorem tot3682 : totK PA10K2 A10K2.t3682 = [0, 474465567861, 1653422149556, 1918887143216, 664291698191, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3683 = true := by
  decide +kernel

theorem tot3683 : totK PA10K2 A10K2.t3683 = [0, 26903710814, 1126504654709, 2406097180811, 1119307263944, 95529618983, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
