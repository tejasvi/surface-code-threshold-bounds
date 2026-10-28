import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2428 = true := by
  decide +kernel

theorem tot2428 : totK PD2M8K2 D2M8K2.t2428 = [0, 0, 170614479357, 447174807230, 255784913780, 22463988627, 0, 0] := by
  decide +kernel

theorem rows2429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2429 = true := by
  decide +kernel

theorem tot2429 : totK PD2M8K2 D2M8K2.t2429 = [0, 0, 157303441568, 445152995577, 273875330065, 21248057791, 0, 0] := by
  decide +kernel

theorem rows2430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2430 = true := by
  decide +kernel

theorem tot2430 : totK PD2M8K2 D2M8K2.t2430 = [0, 0, 89503525964, 363080042074, 360277898637, 57862187330, 1107157161, 0] := by
  decide +kernel

theorem rows2431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2431 = true := by
  decide +kernel

theorem tot2431 : totK PD2M8K2 D2M8K2.t2431 = [0, 0, 0, 299540469229, 462781523619, 107406427200, 3824247485, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
