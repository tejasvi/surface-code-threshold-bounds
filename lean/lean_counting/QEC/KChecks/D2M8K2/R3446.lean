import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13784 = true := by
  decide +kernel

theorem tot13784 : totK PD2M8K2 D2M8K2.t13784 = [48149416567, 228731825788, 420107687327, 164778203474, 10608469453, 0, 0, 0] := by
  decide +kernel

theorem rows13785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13785 = true := by
  decide +kernel

theorem tot13785 : totK PD2M8K2 D2M8K2.t13785 = [196317780588, 465257593792, 244138832706, 23403626011, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13786 = true := by
  decide +kernel

theorem tot13786 : totK PD2M8K2 D2M8K2.t13786 = [175868549765, 472819481739, 229634156546, 12288825511, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13787 = true := by
  decide +kernel

theorem tot13787 : totK PD2M8K2 D2M8K2.t13787 = [0, 289994006028, 500947387137, 109034571487, 1190718505, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
