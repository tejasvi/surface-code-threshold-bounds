import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10920 = true := by
  decide +kernel

theorem tot10920 : totK PD2M8K2 D2M8K2.t10920 = [0, 182497872290, 479374554012, 252231241123, 14901918396, 0, 0, 0] := by
  decide +kernel

theorem rows10921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10921 = true := by
  decide +kernel

theorem tot10921 : totK PD2M8K2 D2M8K2.t10921 = [0, 0, 271471930163, 509786462039, 124228814553, 1268739303, 0, 0] := by
  decide +kernel

theorem rows10922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10922 = true := by
  decide +kernel

theorem tot10922 : totK PD2M8K2 D2M8K2.t10922 = [0, 0, 181152648832, 484209533262, 211340419525, 8669917095, 0, 0] := by
  decide +kernel

theorem rows10923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10923 = true := by
  decide +kernel

theorem tot10923 : totK PD2M8K2 D2M8K2.t10923 = [0, 0, 173756607032, 463166121909, 228954868516, 15756815608, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
