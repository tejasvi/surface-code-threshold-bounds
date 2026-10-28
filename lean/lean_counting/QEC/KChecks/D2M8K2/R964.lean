import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3856 = true := by
  decide +kernel

theorem tot3856 : totK PD2M8K2 D2M8K2.t3856 = [0, 155009944178, 467289046632, 251514165734, 14208386441, 0, 0, 0] := by
  decide +kernel

theorem rows3857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3857 = true := by
  decide +kernel

theorem tot3857 : totK PD2M8K2 D2M8K2.t3857 = [0, 0, 287365259684, 492883994677, 93693612330, 1075657031, 0, 0] := by
  decide +kernel

theorem rows3858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3858 = true := by
  decide +kernel

theorem tot3858 : totK PD2M8K2 D2M8K2.t3858 = [0, 82565466964, 339316516581, 342105533016, 85209842332, 3804183361, 0, 0] := by
  decide +kernel

theorem rows3859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3859 = true := by
  decide +kernel

theorem tot3859 : totK PD2M8K2 D2M8K2.t3859 = [0, 179755076763, 450595815103, 264399282074, 25595410402, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
