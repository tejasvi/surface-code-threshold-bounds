import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2052 = true := by
  decide +kernel

theorem tot2052 : totK PD2M8K2 D2M8K2.t2052 = [0, 65562492737, 327306444480, 405420236922, 91795073235, 1198073392, 0, 0] := by
  decide +kernel

theorem rows2053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2053 = true := by
  decide +kernel

theorem tot2053 : totK PD2M8K2 D2M8K2.t2053 = [0, 0, 203253828443, 487755338231, 181940068600, 9482920370, 0, 0] := by
  decide +kernel

theorem rows2054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2054 = true := by
  decide +kernel

theorem tot2054 : totK PD2M8K2 D2M8K2.t2054 = [0, 172448896236, 447043050524, 238590363305, 42263985198, 2569691499, 0, 0] := by
  decide +kernel

theorem rows2055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2055 = true := by
  decide +kernel

theorem tot2055 : totK PD2M8K2 D2M8K2.t2055 = [0, 170656968623, 430385698535, 260487793807, 27152079091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
