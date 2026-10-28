import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13056 = true := by
  decide +kernel

theorem tot13056 : totK PD2M8K2 D2M8K2.t13056 = [0, 101069471148, 411511239970, 321324340382, 52021813184, 1164319620, 0, 0] := by
  decide +kernel

theorem rows13057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13057 = true := by
  decide +kernel

theorem tot13057 : totK PD2M8K2 D2M8K2.t13057 = [0, 0, 185178083264, 470673757682, 189854443521, 11885407614, 0, 0] := by
  decide +kernel

theorem rows13058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13058 = true := by
  decide +kernel

theorem tot13058 : totK PD2M8K2 D2M8K2.t13058 = [0, 160233838038, 450618446387, 275163382421, 29029639479, 0, 0, 0] := by
  decide +kernel

theorem rows13059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13059 = true := by
  decide +kernel

theorem tot13059 : totK PD2M8K2 D2M8K2.t13059 = [0, 178093191501, 464278138268, 239234346320, 14652289713, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
