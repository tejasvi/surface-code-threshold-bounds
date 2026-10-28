import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15600 = true := by
  decide +kernel

theorem tot15600 : totK PD2M8K2 D2M8K2.t15600 = [0, 0, 182589323308, 477745846775, 248403515621, 17149033700, 0, 0] := by
  decide +kernel

theorem rows15601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15601 = true := by
  decide +kernel

theorem tot15601 : totK PD2M8K2 D2M8K2.t15601 = [0, 0, 174823044453, 474085186406, 232988997900, 13681267370, 0, 0] := by
  decide +kernel

theorem rows15602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15602 = true := by
  decide +kernel

theorem tot15602 : totK PD2M8K2 D2M8K2.t15602 = [0, 0, 0, 268818078460, 488500204971, 114331637840, 2305904642, 0] := by
  decide +kernel

theorem rows15603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15603 = true := by
  decide +kernel

theorem tot15603 : totK PD2M8K2 D2M8K2.t15603 = [0, 0, 50247253896, 241083569182, 386914200954, 158620191289, 10710292732, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
