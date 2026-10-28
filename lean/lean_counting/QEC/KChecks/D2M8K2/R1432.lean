import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5728 = true := by
  decide +kernel

theorem tot5728 : totK PD2M8K2 D2M8K2.t5728 = [0, 178129036519, 453395105921, 257501467841, 28397114714, 0, 0, 0] := by
  decide +kernel

theorem rows5729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5729 = true := by
  decide +kernel

theorem tot5729 : totK PD2M8K2 D2M8K2.t5729 = [0, 195280813066, 469076626121, 225177133745, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows5730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5730 = true := by
  decide +kernel

theorem tot5730 : totK PD2M8K2 D2M8K2.t5730 = [0, 51673496249, 322540767260, 428795422595, 89455981247, 1178750802, 0, 0] := by
  decide +kernel

theorem rows5731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5731 = true := by
  decide +kernel

theorem tot5731 : totK PD2M8K2 D2M8K2.t5731 = [0, 0, 198176170596, 466024021047, 191991488883, 11991925116, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
