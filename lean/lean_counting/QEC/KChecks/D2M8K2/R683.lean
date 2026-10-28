import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2732 = true := by
  decide +kernel

theorem tot2732 : totK PD2M8K2 D2M8K2.t2732 = [0, 162551884278, 475193219234, 260217552082, 15705808181, 0, 0, 0] := by
  decide +kernel

theorem rows2733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2733 = true := by
  decide +kernel

theorem tot2733 : totK PD2M8K2 D2M8K2.t2733 = [0, 0, 180377827804, 456963826682, 246321727822, 24257630845, 0, 0] := by
  decide +kernel

theorem rows2734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2734 = true := by
  decide +kernel

theorem tot2734 : totK PD2M8K2 D2M8K2.t2734 = [0, 0, 195029382079, 491214785733, 211499304656, 6543040663, 0, 0] := by
  decide +kernel

theorem rows2735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2735 = true := by
  decide +kernel

theorem tot2735 : totK PD2M8K2 D2M8K2.t2735 = [0, 160211361594, 366926377272, 249544790072, 98461759243, 6690617053, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
