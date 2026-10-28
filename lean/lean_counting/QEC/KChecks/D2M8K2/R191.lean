import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t764 = true := by
  decide +kernel

theorem tot764 : totK PD2M8K2 D2M8K2.t764 = [0, 116608392078, 446492830221, 306560182506, 22943335060, 0, 0, 0] := by
  decide +kernel

theorem rows765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t765 = true := by
  decide +kernel

theorem tot765 : totK PD2M8K2 D2M8K2.t765 = [0, 29260988630, 283940242563, 481985821790, 96160012182, 1164319620, 0, 0] := by
  decide +kernel

theorem rows766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t766 = true := by
  decide +kernel

theorem tot766 : totK PD2M8K2 D2M8K2.t766 = [0, 192773114086, 467664363297, 231337582671, 19185767080, 0, 0, 0] := by
  decide +kernel

theorem rows767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t767 = true := by
  decide +kernel

theorem tot767 : totK PD2M8K2 D2M8K2.t767 = [0, 187190539096, 470487102234, 222743795901, 12523541424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
