import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2832 = true := by
  decide +kernel

theorem tot2832 : totK PA10K2 A10K2.t2832 = [459144823843, 1847652190834, 1974566536853, 508736319573, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2833 = true := by
  decide +kernel

theorem tot2833 : totK PA10K2 A10K2.t2833 = [0, 739032848094, 2279092075031, 1519830224932, 169341480334, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2834 = true := by
  decide +kernel

theorem tot2834 : totK PA10K2 A10K2.t2834 = [0, 575668655506, 1886689710329, 1843106564755, 521272510782, 32470817489, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2835 = true := by
  decide +kernel

theorem tot2835 : totK PA10K2 A10K2.t2835 = [0, 434687345263, 1713197810162, 2097819172097, 647273131196, 37961772096, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
