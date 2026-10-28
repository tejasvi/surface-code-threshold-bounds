import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14640 = true := by
  decide +kernel

theorem tot14640 : totK PD2M8K2 D2M8K2.t14640 = [0, 203470802579, 455952911168, 239288005807, 26131714756, 0, 0, 0] := by
  decide +kernel

theorem rows14641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14641 = true := by
  decide +kernel

theorem tot14641 : totK PD2M8K2 D2M8K2.t14641 = [0, 174943586052, 462238398285, 238087273350, 16797468201, 0, 0, 0] := by
  decide +kernel

theorem rows14642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14642 = true := by
  decide +kernel

theorem tot14642 : totK PD2M8K2 D2M8K2.t14642 = [0, 0, 356180903584, 498219605133, 65250382164, 0, 0, 0] := by
  decide +kernel

theorem rows14643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14643 = true := by
  decide +kernel

theorem tot14643 : totK PD2M8K2 D2M8K2.t14643 = [0, 128545043771, 356270687476, 315496249492, 91031326730, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
