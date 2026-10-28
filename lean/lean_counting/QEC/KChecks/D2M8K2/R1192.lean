import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4768 = true := by
  decide +kernel

theorem tot4768 : totK PD2M8K2 D2M8K2.t4768 = [0, 0, 214004644127, 489051488069, 176432521822, 9482920370, 0, 0] := by
  decide +kernel

theorem rows4769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4769 = true := by
  decide +kernel

theorem tot4769 : totK PD2M8K2 D2M8K2.t4769 = [0, 172401869485, 437487303013, 241181999572, 45514112254, 2569691499, 0, 0] := by
  decide +kernel

theorem rows4770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4770 = true := by
  decide +kernel

theorem tot4770 : totK PD2M8K2 D2M8K2.t4770 = [0, 170615067624, 434987158350, 269102283342, 30211850834, 0, 0, 0] := by
  decide +kernel

theorem rows4771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4771 = true := by
  decide +kernel

theorem tot4771 : totK PD2M8K2 D2M8K2.t4771 = [0, 92722817510, 390708207286, 348125212356, 52987877616, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
