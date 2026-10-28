import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t152 = true := by
  decide +kernel

theorem tot152 : totK PA10K2 A10K2.t152 = [0, 0, 461417741280, 1812420216587, 1772810663375, 436968260938, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t153 = true := by
  decide +kernel

theorem tot153 : totK PA10K2 A10K2.t153 = [0, 413708365145, 1623574929763, 1982088866141, 756944282348, 109153042362, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t154 = true := by
  decide +kernel

theorem tot154 : totK PA10K2 A10K2.t154 = [0, 138992330854, 1217213923285, 2227454732691, 968054311776, 71494099762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t155 = true := by
  decide +kernel

theorem tot155 : totK PA10K2 A10K2.t155 = [0, 494801160783, 1703147567308, 1798360484688, 761909178654, 141497682970, 5546304973, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
