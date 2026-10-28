import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11768 = true := by
  decide +kernel

theorem tot11768 : totK PD2M8K2 D2M8K2.t11768 = [0, 89913613664, 298838910626, 386322242418, 115811005127, 5874298072, 0, 0] := by
  decide +kernel

theorem rows11769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11769 = true := by
  decide +kernel

theorem tot11769 : totK PD2M8K2 D2M8K2.t11769 = [0, 170931542162, 435961764563, 282511547981, 30536180053, 0, 0, 0] := by
  decide +kernel

theorem rows11770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11770 = true := by
  decide +kernel

theorem tot11770 : totK PD2M8K2 D2M8K2.t11770 = [0, 69897370391, 423409296447, 380996390338, 49891246533, 0, 0, 0] := by
  decide +kernel

theorem rows11771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11771 = true := by
  decide +kernel

theorem tot11771 : totK PD2M8K2 D2M8K2.t11771 = [0, 27834298272, 216945449076, 468835712027, 165303085732, 5439011083, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
