import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15432 = true := by
  decide +kernel

theorem tot15432 : totK PD2M8K2 D2M8K2.t15432 = [0, 0, 0, 217964300759, 473239276129, 175030440580, 8235505476, 0] := by
  decide +kernel

theorem rows15433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15433 = true := by
  decide +kernel

theorem tot15433 : totK PD2M8K2 D2M8K2.t15433 = [0, 0, 88972803789, 349884758348, 362348759368, 74295421658, 1291861884, 0] := by
  decide +kernel

theorem rows15434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15434 = true := by
  decide +kernel

theorem tot15434 : totK PD2M8K2 D2M8K2.t15434 = [0, 0, 200005823867, 483262124775, 220464031779, 12234559058, 0, 0] := by
  decide +kernel

theorem rows15435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15435 = true := by
  decide +kernel

theorem tot15435 : totK PD2M8K2 D2M8K2.t15435 = [0, 0, 88522936701, 424080888496, 351996077113, 26448079266, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
