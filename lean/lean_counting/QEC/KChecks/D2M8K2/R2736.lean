import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10944 = true := by
  decide +kernel

theorem tot10944 : totK PD2M8K2 D2M8K2.t10944 = [37194636605, 344678118409, 477840723949, 62687453828, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10945 = true := by
  decide +kernel

theorem tot10945 : totK PD2M8K2 D2M8K2.t10945 = [202128012519, 462032637003, 221877727573, 18017314273, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10946 = true := by
  decide +kernel

theorem tot10946 : totK PD2M8K2 D2M8K2.t10946 = [177286973961, 467943600048, 226800667364, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows10947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10947 = true := by
  decide +kernel

theorem tot10947 : totK PD2M8K2 D2M8K2.t10947 = [0, 283628159110, 496240977673, 105033530490, 1164319620, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
