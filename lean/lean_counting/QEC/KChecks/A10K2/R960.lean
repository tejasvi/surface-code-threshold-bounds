import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3840 = true := by
  decide +kernel

theorem tot3840 : totK PA10K2 A10K2.t3840 = [0, 0, 582523478866, 1941353772191, 1789456039951, 449117452151, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows3841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3841 = true := by
  decide +kernel

theorem tot3841 : totK PA10K2 A10K2.t3841 = [0, 0, 0, 941789987340, 2385147079396, 1254809426140, 113943173993, 0, 0, 0] := by
  decide +kernel

theorem rows3842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3842 = true := by
  decide +kernel

theorem tot3842 : totK PA10K2 A10K2.t3842 = [0, 0, 0, 496618793438, 1822202426166, 1807041724287, 456049883763, 31987755669, 0, 0] := by
  decide +kernel

theorem rows3843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3843 = true := by
  decide +kernel

theorem tot3843 : totK PA10K2 A10K2.t3843 = [0, 0, 0, 600991218023, 2026129757002, 1766756376100, 294342898866, 6354603908, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
