import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11372 = true := by
  decide +kernel

theorem tot11372 : totK PD2M8K2 D2M8K2.t11372 = [192761384623, 462133445732, 231743432089, 16330485874, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11373 = true := by
  decide +kernel

theorem tot11373 : totK PD2M8K2 D2M8K2.t11373 = [19735703396, 315452125563, 466300153767, 104609096042, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11374 = true := by
  decide +kernel

theorem tot11374 : totK PD2M8K2 D2M8K2.t11374 = [0, 206863918587, 478232652364, 185196453040, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows11375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11375 = true := by
  decide +kernel

theorem tot11375 : totK PD2M8K2 D2M8K2.t11375 = [0, 152792428942, 432359160706, 292416748554, 35264720815, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
