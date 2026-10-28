import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8008 = true := by
  decide +kernel

theorem tot8008 : totK PD2M8K2 D2M8K2.t8008 = [0, 0, 225107560113, 494108747145, 194030930853, 11327961991, 0, 0] := by
  decide +kernel

theorem rows8009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8009 = true := by
  decide +kernel

theorem tot8009 : totK PD2M8K2 D2M8K2.t8009 = [0, 0, 221366500125, 491811659236, 192685365142, 11312028820, 0, 0] := by
  decide +kernel

theorem rows8010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8010 = true := by
  decide +kernel

theorem tot8010 : totK PD2M8K2 D2M8K2.t8010 = [0, 0, 180586027990, 472856250420, 242990458088, 12283117284, 0, 0] := by
  decide +kernel

theorem rows8011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8011 = true := by
  decide +kernel

theorem tot8011 : totK PD2M8K2 D2M8K2.t8011 = [0, 0, 205493515157, 457350820336, 209089642380, 10929066306, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
